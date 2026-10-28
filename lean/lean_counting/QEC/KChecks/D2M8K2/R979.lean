import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3916 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3916 = true := by
  decide +kernel

theorem tot3916 : totK PD2M8K2 D2M8K2.t3916 = [0, 92986855429, 388775265613, 391598934710, 50070730916, 0, 0, 0] := by
  decide +kernel

theorem rows3917 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3917 = true := by
  decide +kernel

theorem tot3917 : totK PD2M8K2 D2M8K2.t3917 = [0, 188416184150, 459804243444, 252515830599, 19898995873, 0, 0, 0] := by
  decide +kernel

theorem rows3918 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3918 = true := by
  decide +kernel

theorem tot3918 : totK PD2M8K2 D2M8K2.t3918 = [0, 139248936037, 453576780437, 289440988077, 31277816181, 0, 0, 0] := by
  decide +kernel

theorem rows3919 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3919 = true := by
  decide +kernel

theorem tot3919 : totK PD2M8K2 D2M8K2.t3919 = [0, 0, 173532789025, 449712931601, 257784773438, 23329198674, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
