import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5312 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5312 = true := by
  decide +kernel

theorem tot5312 : totK PD2M8K2 D2M8K2.t5312 = [0, 130554847793, 397623051183, 357135064467, 47179712098, 0, 0, 0] := by
  decide +kernel

theorem rows5313 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5313 = true := by
  decide +kernel

theorem tot5313 : totK PD2M8K2 D2M8K2.t5313 = [0, 201775666324, 483378943073, 221107700059, 14605981620, 0, 0, 0] := by
  decide +kernel

theorem rows5314 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5314 = true := by
  decide +kernel

theorem tot5314 : totK PD2M8K2 D2M8K2.t5314 = [0, 88459214294, 393553694514, 371512896374, 64506852778, 3626128243, 0, 0] := by
  decide +kernel

theorem rows5315 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5315 = true := by
  decide +kernel

theorem tot5315 : totK PD2M8K2 D2M8K2.t5315 = [0, 0, 158871470601, 449182933253, 275476524550, 22886833259, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
