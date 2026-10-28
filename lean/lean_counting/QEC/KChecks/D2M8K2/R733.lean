import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2932 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2932 = true := by
  decide +kernel

theorem tot2932 : totK PD2M8K2 D2M8K2.t2932 = [88470648217, 348560585382, 370430374018, 79832940720, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows2933 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2933 = true := by
  decide +kernel

theorem tot2933 : totK PD2M8K2 D2M8K2.t2933 = [34537017422, 330748792648, 484971139131, 68641403693, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2934 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2934 = true := by
  decide +kernel

theorem tot2934 : totK PD2M8K2 D2M8K2.t2934 = [160315859645, 444987336216, 276625110434, 30318485251, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2935 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2935 = true := by
  decide +kernel

theorem tot2935 : totK PD2M8K2 D2M8K2.t2935 = [218366578183, 495819012422, 204720776516, 9910387013, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
