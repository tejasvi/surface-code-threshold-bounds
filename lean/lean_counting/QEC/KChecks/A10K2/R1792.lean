import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7168 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7168 = true := by
  decide +kernel

theorem tot7168 : totK PA10K2 A10K2.t7168 = [0, 112037851608, 817344724963, 1905872047234, 1583166745928, 316271355956, 10760911071, 0, 0, 0] := by
  decide +kernel

theorem rows7169 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7169 = true := by
  decide +kernel

theorem tot7169 : totK PA10K2 A10K2.t7169 = [0, 519204680828, 1721723386302, 1851847163991, 621046361032, 52230035883, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7170 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7170 = true := by
  decide +kernel

theorem tot7170 : totK PA10K2 A10K2.t7170 = [0, 118685722320, 1252577329899, 2281892472537, 995476486109, 81378533866, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7171 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7171 = true := by
  decide +kernel

theorem tot7171 : totK PA10K2 A10K2.t7171 = [0, 297392362862, 1216559781351, 1861485618616, 1142858335370, 219727073494, 6354482628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
