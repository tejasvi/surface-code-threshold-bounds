import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13000 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13000 = true := by
  decide +kernel

theorem tot13000 : totK PD2M8K2 D2M8K2.t13000 = [0, 0, 254946913718, 507568575583, 132063033349, 2309606161, 0, 0] := by
  decide +kernel

theorem rows13001 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13001 = true := by
  decide +kernel

theorem tot13001 : totK PD2M8K2 D2M8K2.t13001 = [0, 67923955290, 246280149153, 399563161941, 155506081810, 10740121073, 0, 0] := by
  decide +kernel

theorem rows13002 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13002 = true := by
  decide +kernel

theorem tot13002 : totK PD2M8K2 D2M8K2.t13002 = [0, 187016165613, 479424754375, 229837650117, 16493134775, 0, 0, 0] := by
  decide +kernel

theorem rows13003 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13003 = true := by
  decide +kernel

theorem tot13003 : totK PD2M8K2 D2M8K2.t13003 = [0, 88410714321, 385519563373, 351234263825, 55378142452, 1198073392, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
