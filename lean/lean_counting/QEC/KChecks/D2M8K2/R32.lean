import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows128 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t128 = true := by
  decide +kernel

theorem tot128 : totK PD2M8K2 D2M8K2.t128 = [0, 185999672057, 479501269974, 214801200153, 11460472315, 0, 0, 0] := by
  decide +kernel

theorem rows129 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t129 = true := by
  decide +kernel

theorem tot129 : totK PD2M8K2 D2M8K2.t129 = [0, 169528560583, 469467611159, 244146965393, 15786853068, 0, 0, 0] := by
  decide +kernel

theorem rows130 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t130 = true := by
  decide +kernel

theorem tot130 : totK PD2M8K2 D2M8K2.t130 = [0, 190876433099, 465253218986, 217553605429, 10110512227, 0, 0, 0] := by
  decide +kernel

theorem rows131 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t131 = true := by
  decide +kernel

theorem tot131 : totK PD2M8K2 D2M8K2.t131 = [0, 197696810721, 482628203454, 210336845252, 11066126582, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
