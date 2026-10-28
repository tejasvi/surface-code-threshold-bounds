import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8104 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8104 = true := by
  decide +kernel

theorem tot8104 : totK PA10K2 A10K2.t8104 = [0, 0, 0, 522942771495, 1735584289626, 1899555597289, 741388442417, 68134776494, 0, 0] := by
  decide +kernel

theorem rows8105 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8105 = true := by
  decide +kernel

theorem tot8105 : totK PA10K2 A10K2.t8105 = [0, 0, 0, 344104374613, 1658524372833, 2216213588167, 773127705362, 37025427889, 0, 0] := by
  decide +kernel

theorem rows8106 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8106 = true := by
  decide +kernel

theorem tot8106 : totK PA10K2 A10K2.t8106 = [0, 0, 0, 0, 537125438212, 1973054967172, 1980570505188, 425864241074, 13244237517, 0] := by
  decide +kernel

theorem rows8107 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8107 = true := by
  decide +kernel

theorem tot8107 : totK PA10K2 A10K2.t8107 = [0, 0, 310694887869, 690619871721, 641984770615, 1240060906500, 1456190278649, 556237602492, 49137922124, 0] := by
  decide +kernel

end QECKChecks.A10K2
