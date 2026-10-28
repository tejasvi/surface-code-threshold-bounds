import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15544 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15544 = true := by
  decide +kernel

theorem tot15544 : totK PD2M8K2 D2M8K2.t15544 = [0, 153907372348, 471253647856, 282150168719, 16275136355, 0, 0, 0] := by
  decide +kernel

theorem rows15545 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15545 = true := by
  decide +kernel

theorem tot15545 : totK PD2M8K2 D2M8K2.t15545 = [0, 0, 244977039983, 504852665909, 157879155151, 7053496397, 0, 0] := by
  decide +kernel

theorem rows15546 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15546 = true := by
  decide +kernel

theorem tot15546 : totK PD2M8K2 D2M8K2.t15546 = [0, 141309891445, 397563540407, 303966485299, 70265683411, 1334898114, 0, 0] := by
  decide +kernel

theorem rows15547 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15547 = true := by
  decide +kernel

theorem tot15547 : totK PD2M8K2 D2M8K2.t15547 = [0, 156085976310, 444843421561, 292669540226, 23521472693, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
