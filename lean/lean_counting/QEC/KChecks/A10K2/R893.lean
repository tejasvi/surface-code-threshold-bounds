import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3572 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3572 = true := by
  decide +kernel

theorem tot3572 : totK PA10K2 A10K2.t3572 = [0, 301365846009, 1096754677831, 1696117350351, 1528684739090, 469279507235, 30829329317, 0, 0, 0] := by
  decide +kernel

theorem rows3573 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3573 = true := by
  decide +kernel

theorem tot3573 : totK PA10K2 A10K2.t3573 = [0, 465698138976, 1779197032831, 1972652748934, 570427366825, 32040661968, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3574 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3574 = true := by
  decide +kernel

theorem tot3574 : totK PA10K2 A10K2.t3574 = [0, 0, 685003906640, 2083519174770, 1652020866612, 385978274734, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows3575 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3575 = true := by
  decide +kernel

theorem tot3575 : totK PA10K2 A10K2.t3575 = [0, 279016151902, 1231067131129, 1911238177542, 1207788041167, 202209258280, 5460492893, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
