import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4764 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4764 = true := by
  decide +kernel

theorem tot4764 : totK PD2M8K2 D2M8K2.t4764 = [0, 0, 236123016838, 494211932778, 160721955924, 9404247146, 0, 0] := by
  decide +kernel

theorem rows4765 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4765 = true := by
  decide +kernel

theorem tot4765 : totK PD2M8K2 D2M8K2.t4765 = [0, 171060998881, 422211947056, 250234712509, 46828550662, 2481160468, 0, 0] := by
  decide +kernel

theorem rows4766 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4766 = true := by
  decide +kernel

theorem tot4766 : totK PD2M8K2 D2M8K2.t4766 = [0, 180894072074, 476129165006, 238231531319, 15031594354, 0, 0, 0] := by
  decide +kernel

theorem rows4767 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4767 = true := by
  decide +kernel

theorem tot4767 : totK PD2M8K2 D2M8K2.t4767 = [0, 71870147678, 319877143902, 400230735416, 90980436055, 1198073392, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
