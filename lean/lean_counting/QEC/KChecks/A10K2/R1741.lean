import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6964 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6964 = true := by
  decide +kernel

theorem tot6964 : totK PA10K2 A10K2.t6964 = [0, 493468057342, 1837178694126, 1940121130988, 543755392192, 32192334608, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6965 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6965 = true := by
  decide +kernel

theorem tot6965 : totK PA10K2 A10K2.t6965 = [0, 227459092167, 1265101646197, 2191180185448, 1244020732746, 145014612571, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6966 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6966 = true := by
  decide +kernel

theorem tot6966 : totK PA10K2 A10K2.t6966 = [0, 104360546894, 736610776684, 1809557736553, 1633472820917, 463101773045, 31522233512, 0, 0, 0] := by
  decide +kernel

theorem rows6967 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6967 = true := by
  decide +kernel

theorem tot6967 : totK PA10K2 A10K2.t6967 = [0, 507960903198, 1830242729229, 2010673308595, 616492659653, 42355672685, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
