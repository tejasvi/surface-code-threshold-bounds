import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10188 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10188 = true := by
  decide +kernel

theorem tot10188 : totK PD2M8K2 D2M8K2.t10188 = [0, 0, 175697644231, 451621539158, 265908400297, 27414016875, 0, 0] := by
  decide +kernel

theorem rows10189 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10189 = true := by
  decide +kernel

theorem tot10189 : totK PD2M8K2 D2M8K2.t10189 = [0, 0, 191857419668, 473565098980, 223832890730, 11458754655, 0, 0] := by
  decide +kernel

theorem rows10190 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10190 = true := by
  decide +kernel

theorem tot10190 : totK PD2M8K2 D2M8K2.t10190 = [0, 0, 67793698003, 336794746927, 401423127637, 86549352010, 1242138600, 0] := by
  decide +kernel

theorem rows10191 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10191 = true := by
  decide +kernel

theorem tot10191 : totK PD2M8K2 D2M8K2.t10191 = [0, 0, 0, 230845654528, 484308225543, 148445833780, 4948628341, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
