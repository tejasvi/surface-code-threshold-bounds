import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9044 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9044 = true := by
  decide +kernel

theorem tot9044 : totK PD2M8K2 D2M8K2.t9044 = [0, 94308289763, 283128754100, 366490273752, 168795068056, 11693999300, 0, 0] := by
  decide +kernel

theorem rows9045 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9045 = true := by
  decide +kernel

theorem tot9045 : totK PD2M8K2 D2M8K2.t9045 = [0, 173118726115, 456269406510, 269414457762, 19543046160, 0, 0, 0] := by
  decide +kernel

theorem rows9046 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9046 = true := by
  decide +kernel

theorem tot9046 : totK PD2M8K2 D2M8K2.t9046 = [0, 176425804272, 472340965753, 245529411178, 12670836095, 0, 0, 0] := by
  decide +kernel

theorem rows9047 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9047 = true := by
  decide +kernel

theorem tot9047 : totK PD2M8K2 D2M8K2.t9047 = [0, 0, 193541546427, 455712765650, 239694853049, 24216995793, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
