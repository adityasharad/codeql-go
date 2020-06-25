/**
 * @name Function call using untrusted input
 * @description Exploratory analysis that looks for untrusted input that may reach the arguments of a function call.
 * @kind path-problem
 * @problem.severity recommendation
 * @precision low
 * @id go/untrusted-flow
 */

import go
import DataFlow::PathGraph

/**
 * A function parameter of type `* ...Request`.
 * These are likely to be protobuf message requests to an external-facing API,
 * and so are considered untrusted input.
 */
class RequestParameter extends DataFlow::ParameterNode, UntrustedFlowSource {
  RequestParameter() { this.getType().(PointerType).getBaseType().getName().matches("%Request") }
}

/** Track the flow of taint from `x` to `x.Get*()`. */
class GetterTaintStep extends TaintTracking::AdditionalTaintStep {
  override predicate step(DataFlow::Node node1, DataFlow::Node node2) {
    exists(DataFlow::CallNode getterCall |
      getterCall.getCalleeName().matches("Get%") and
      node1 = getterCall.getReceiver() and
      node2 = getterCall
    )
  }
}

class UntrustedFlowConfig extends TaintTracking::Configuration {
  UntrustedFlowConfig() { this = "UntrustedFlowConfig" }

  override predicate isSource(DataFlow::Node source) { source instanceof UntrustedFlowSource }

  override predicate isSink(DataFlow::Node sink) {
    sink = any(DataFlow::CallNode call).getAnArgument()
  }
}

from UntrustedFlowConfig cfg, DataFlow::PathNode source, DataFlow::PathNode sink
where cfg.hasFlowPath(source, sink)
select sink, source, sink, "$@ reaches this function call argument.", source.getNode(),
  "Untrusted input"
