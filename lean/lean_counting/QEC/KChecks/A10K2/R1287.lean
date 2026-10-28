import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5148 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5148 = true := by
  decide +kernel

theorem tot5148 : totK PA10K2 A10K2.t5148 = [0, 0, 529118203987, 1837462575797, 1877742280045, 449557017785, 31169761322, 0, 0, 0] := by
  decide +kernel

theorem rows5149 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5149 = true := by
  decide +kernel

theorem tot5149 : totK PA10K2 A10K2.t5149 = [0, 0, 395103114261, 1770930320425, 2009170380434, 522724856381, 31889781550, 0, 0, 0] := by
  decide +kernel

theorem rows5150 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5150 = true := by
  decide +kernel

theorem tot5150 : totK PA10K2 A10K2.t5150 = [0, 0, 0, 756173596386, 2198715881599, 1408662991607, 198149694690, 0, 0, 0] := by
  decide +kernel

theorem rows5151 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5151 = true := by
  decide +kernel

theorem tot5151 : totK PA10K2 A10K2.t5151 = [0, 0, 578189715567, 1900906731066, 1727532824656, 457472976494, 86953411738, 6354482628, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
