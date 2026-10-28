import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15988 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15988 = true := by
  decide +kernel

theorem tot15988 : totK PD2M8K2 D2M8K2.t15988 = [0, 0, 52337025351, 380155788857, 430108753358, 59204662894, 0, 0] := by
  decide +kernel

theorem rows15989 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15989 = true := by
  decide +kernel

theorem tot15989 : totK PD2M8K2 D2M8K2.t15989 = [0, 0, 71399612449, 288754790718, 417742390783, 121521218512, 4254338973, 0] := by
  decide +kernel

theorem rows15990 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15990 = true := by
  decide +kernel

theorem tot15990 : totK PD2M8K2 D2M8K2.t15990 = [0, 0, 221742447171, 469561083202, 219306542553, 23204368665, 0, 0] := by
  decide +kernel

theorem rows15991 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15991 = true := by
  decide +kernel

theorem tot15991 : totK PD2M8K2 D2M8K2.t15991 = [0, 0, 186701378369, 484570881255, 218881736277, 11556542072, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
