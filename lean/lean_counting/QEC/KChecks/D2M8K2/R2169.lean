import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8676 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8676 = true := by
  decide +kernel

theorem tot8676 : totK PD2M8K2 D2M8K2.t8676 = [0, 188889113419, 479476734348, 221040390924, 12433893103, 0, 0, 0] := by
  decide +kernel

theorem rows8677 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8677 = true := by
  decide +kernel

theorem tot8677 : totK PD2M8K2 D2M8K2.t8677 = [0, 56667572818, 350748670233, 427267826412, 75220267874, 0, 0, 0] := by
  decide +kernel

theorem rows8678 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8678 = true := by
  decide +kernel

theorem tot8678 : totK PD2M8K2 D2M8K2.t8678 = [0, 0, 192542027398, 471234377344, 191634625900, 8824320960, 0, 0] := by
  decide +kernel

theorem rows8679 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8679 = true := by
  decide +kernel

theorem tot8679 : totK PD2M8K2 D2M8K2.t8679 = [0, 155281256290, 438853553477, 282127123547, 40344331691, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
