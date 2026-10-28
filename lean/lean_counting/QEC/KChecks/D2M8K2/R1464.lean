import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5856 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5856 = true := by
  decide +kernel

theorem tot5856 : totK PD2M8K2 D2M8K2.t5856 = [195780359382, 476444740798, 221381347046, 12206405976, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5857 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5857 = true := by
  decide +kernel

theorem tot5857 : totK PD2M8K2 D2M8K2.t5857 = [0, 256462352570, 442369815852, 193410862219, 21393864572, 0, 0, 0] := by
  decide +kernel

theorem rows5858 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5858 = true := by
  decide +kernel

theorem tot5858 : totK PD2M8K2 D2M8K2.t5858 = [0, 192526817154, 484802423989, 212392892962, 7991928755, 0, 0, 0] := by
  decide +kernel

theorem rows5859 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5859 = true := by
  decide +kernel

theorem tot5859 : totK PD2M8K2 D2M8K2.t5859 = [91239674996, 290204030393, 348412836388, 160655236960, 8209296672, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
