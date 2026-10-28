import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16244 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16244 = true := by
  decide +kernel

theorem tot16244 : totK PD2M8K2 D2M8K2.t16244 = [0, 0, 51620336044, 288391045537, 440491110941, 109612146235, 4008488258, 0] := by
  decide +kernel

theorem rows16245 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16245 = true := by
  decide +kernel

theorem tot16245 : totK PD2M8K2 D2M8K2.t16245 = [0, 0, 196040486545, 479967489080, 220735316872, 14571387952, 0, 0] := by
  decide +kernel

theorem rows16246 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16246 = true := by
  decide +kernel

theorem tot16246 : totK PD2M8K2 D2M8K2.t16246 = [0, 0, 163345080708, 470768523232, 241799506922, 11689024843, 0, 0] := by
  decide +kernel

theorem rows16247 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16247 = true := by
  decide +kernel

theorem tot16247 : totK PD2M8K2 D2M8K2.t16247 = [0, 0, 0, 271080489528, 510236169277, 108801574228, 1198073392, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
