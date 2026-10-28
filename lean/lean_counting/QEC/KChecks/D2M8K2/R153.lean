import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows612 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t612 = true := by
  decide +kernel

theorem tot612 : totK PD2M8K2 D2M8K2.t612 = [0, 182185895241, 476572583763, 230398123849, 12885670648, 0, 0, 0] := by
  decide +kernel

theorem rows613 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t613 = true := by
  decide +kernel

theorem tot613 : totK PD2M8K2 D2M8K2.t613 = [0, 191759825614, 470763098993, 226661219944, 12679943201, 0, 0, 0] := by
  decide +kernel

theorem rows614 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t614 = true := by
  decide +kernel

theorem tot614 : totK PD2M8K2 D2M8K2.t614 = [0, 192478416136, 470710936018, 213174736328, 12595094539, 0, 0, 0] := by
  decide +kernel

theorem rows615 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t615 = true := by
  decide +kernel

theorem tot615 : totK PD2M8K2 D2M8K2.t615 = [0, 167103277493, 479708137775, 222225107522, 8671967938, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
