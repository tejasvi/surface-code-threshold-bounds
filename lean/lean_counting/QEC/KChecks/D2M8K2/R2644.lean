import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10576 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10576 = true := by
  decide +kernel

theorem tot10576 : totK PD2M8K2 D2M8K2.t10576 = [0, 0, 212770202525, 486850796552, 182168417552, 9587713104, 0, 0] := by
  decide +kernel

theorem rows10577 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10577 = true := by
  decide +kernel

theorem tot10577 : totK PD2M8K2 D2M8K2.t10577 = [0, 83813933705, 323462427228, 378184278365, 94452063749, 3462014130, 0, 0] := by
  decide +kernel

theorem rows10578 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10578 = true := by
  decide +kernel

theorem tot10578 : totK PD2M8K2 D2M8K2.t10578 = [0, 176041716236, 451949784144, 262130755018, 27460954080, 0, 0, 0] := by
  decide +kernel

theorem rows10579 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10579 = true := by
  decide +kernel

theorem tot10579 : totK PD2M8K2 D2M8K2.t10579 = [0, 163431418577, 466249535996, 250994302543, 14978238975, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
