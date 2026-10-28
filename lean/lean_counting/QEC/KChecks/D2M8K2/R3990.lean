import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15960 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15960 = true := by
  decide +kernel

theorem tot15960 : totK PD2M8K2 D2M8K2.t15960 = [0, 0, 194685301052, 467235309401, 214070791150, 12523541424, 0, 0] := by
  decide +kernel

theorem rows15961 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15961 = true := by
  decide +kernel

theorem tot15961 : totK PD2M8K2 D2M8K2.t15961 = [0, 0, 26409388158, 316356941139, 458315233892, 92062673903, 1198073392, 0] := by
  decide +kernel

theorem rows15962 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15962 = true := by
  decide +kernel

theorem tot15962 : totK PD2M8K2 D2M8K2.t15962 = [0, 0, 24216773411, 271812036110, 470657192567, 124089978613, 4257574148, 0] := by
  decide +kernel

theorem rows15963 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15963 = true := by
  decide +kernel

theorem tot15963 : totK PD2M8K2 D2M8K2.t15963 = [0, 0, 208522341504, 491555088003, 188306037365, 3926024352, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
