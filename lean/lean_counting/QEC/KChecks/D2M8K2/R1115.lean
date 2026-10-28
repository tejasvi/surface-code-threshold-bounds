import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4460 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4460 = true := by
  decide +kernel

theorem tot4460 : totK PD2M8K2 D2M8K2.t4460 = [0, 0, 175521683754, 473317357728, 238921633276, 13291781812, 0, 0] := by
  decide +kernel

theorem rows4461 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4461 = true := by
  decide +kernel

theorem tot4461 : totK PD2M8K2 D2M8K2.t4461 = [0, 0, 0, 293512832955, 486703350993, 98903895511, 1162935789, 0] := by
  decide +kernel

theorem rows4462 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4462 = true := by
  decide +kernel

theorem tot4462 : totK PD2M8K2 D2M8K2.t4462 = [0, 0, 36272210802, 222645449536, 407503748540, 175695711152, 11853261585, 0] := by
  decide +kernel

theorem rows4463 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4463 = true := by
  decide +kernel

theorem tot4463 : totK PD2M8K2 D2M8K2.t4463 = [0, 0, 199443633174, 474628349773, 211590231322, 11056080877, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
