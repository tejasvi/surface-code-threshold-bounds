import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13868 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13868 = true := by
  decide +kernel

theorem tot13868 : totK PD2M8K2 D2M8K2.t13868 = [170245412399, 459174561809, 269524087662, 24322886038, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13869 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13869 = true := by
  decide +kernel

theorem tot13869 : totK PD2M8K2 D2M8K2.t13869 = [181257342552, 478641894133, 246308740944, 14460774300, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13870 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13870 = true := by
  decide +kernel

theorem tot13870 : totK PD2M8K2 D2M8K2.t13870 = [0, 273799307166, 507199190230, 121415240191, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows13871 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13871 = true := by
  decide +kernel

theorem tot13871 : totK PD2M8K2 D2M8K2.t13871 = [0, 180144277397, 483877531389, 212896422902, 8643947750, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
