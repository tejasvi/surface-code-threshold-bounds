import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows104 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t104 = true := by
  decide +kernel

theorem tot104 : totK PD2M8K2 D2M8K2.t104 = [201667284131, 479627678934, 208751176473, 9852138406, 0, 0, 0, 0] := by
  decide +kernel

theorem rows105 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t105 = true := by
  decide +kernel

theorem tot105 : totK PD2M8K2 D2M8K2.t105 = [190044515459, 474757697744, 218094490337, 12534051746, 0, 0, 0, 0] := by
  decide +kernel

theorem rows106 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t106 = true := by
  decide +kernel

theorem tot106 : totK PD2M8K2 D2M8K2.t106 = [0, 287403279707, 490151198270, 106855927518, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows107 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t107 = true := by
  decide +kernel

theorem tot107 : totK PD2M8K2 D2M8K2.t107 = [73284665194, 370949732780, 417426548697, 55685245790, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
