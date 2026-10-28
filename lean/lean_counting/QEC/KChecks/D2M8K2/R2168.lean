import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8672 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8672 = true := by
  decide +kernel

theorem tot8672 : totK PD2M8K2 D2M8K2.t8672 = [0, 182458817458, 468233559158, 223645344904, 12132121634, 0, 0, 0] := by
  decide +kernel

theorem rows8673 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8673 = true := by
  decide +kernel

theorem tot8673 : totK PD2M8K2 D2M8K2.t8673 = [0, 52582310646, 344732041720, 428792912611, 73059907071, 0, 0, 0] := by
  decide +kernel

theorem rows8674 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8674 = true := by
  decide +kernel

theorem tot8674 : totK PD2M8K2 D2M8K2.t8674 = [0, 0, 191798558370, 471013197887, 188621088794, 8706415949, 0, 0] := by
  decide +kernel

theorem rows8675 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8675 = true := by
  decide +kernel

theorem tot8675 : totK PD2M8K2 D2M8K2.t8675 = [0, 171089712959, 447655633299, 277307719994, 31500626454, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
