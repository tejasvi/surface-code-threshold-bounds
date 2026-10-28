import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5300 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5300 = true := by
  decide +kernel

theorem tot5300 : totK PD2M8K2 D2M8K2.t5300 = [0, 0, 182155647271, 480520779923, 241033784925, 15955732371, 0, 0] := by
  decide +kernel

theorem rows5301 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5301 = true := by
  decide +kernel

theorem tot5301 : totK PD2M8K2 D2M8K2.t5301 = [0, 0, 170755953238, 463862499038, 244037751335, 14874568699, 0, 0] := by
  decide +kernel

theorem rows5302 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5302 = true := by
  decide +kernel

theorem tot5302 : totK PD2M8K2 D2M8K2.t5302 = [0, 0, 0, 273902222281, 490380429206, 106557580658, 1162935789, 0] := by
  decide +kernel

theorem rows5303 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5303 = true := by
  decide +kernel

theorem tot5303 : totK PD2M8K2 D2M8K2.t5303 = [0, 0, 66172613228, 257545608505, 380917960113, 149185110437, 8304610187, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
