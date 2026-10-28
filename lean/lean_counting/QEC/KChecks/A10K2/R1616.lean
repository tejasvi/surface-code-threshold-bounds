import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6464 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6464 = true := by
  decide +kernel

theorem tot6464 : totK PA10K2 A10K2.t6464 = [0, 561835835389, 1949536669994, 1873570975843, 463325035598, 25998226885, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6465 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6465 = true := by
  decide +kernel

theorem tot6465 : totK PA10K2 A10K2.t6465 = [0, 119585100515, 1093988630447, 2149901885229, 1360695052473, 262341293272, 12219140272, 0, 0, 0] := by
  decide +kernel

theorem rows6466 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6466 = true := by
  decide +kernel

theorem tot6466 : totK PA10K2 A10K2.t6466 = [0, 268279236603, 1122603495240, 1904615047986, 1416710347072, 215500105296, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6467 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6467 = true := by
  decide +kernel

theorem tot6467 : totK PA10K2 A10K2.t6467 = [0, 490917962038, 1792151622090, 2027703663478, 633714683820, 33480773222, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
