import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8904 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8904 = true := by
  decide +kernel

theorem tot8904 : totK PD2M8K2 D2M8K2.t8904 = [0, 179238291557, 467069672320, 254233491510, 14459426280, 0, 0, 0] := by
  decide +kernel

theorem rows8905 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8905 = true := by
  decide +kernel

theorem tot8905 : totK PD2M8K2 D2M8K2.t8905 = [0, 0, 297529184813, 477397825379, 115113924746, 1238673482, 0, 0] := by
  decide +kernel

theorem rows8906 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8906 = true := by
  decide +kernel

theorem tot8906 : totK PD2M8K2 D2M8K2.t8906 = [90526249043, 147180496895, 133821851770, 342748533227, 161247805254, 8063697217, 0, 0] := by
  decide +kernel

theorem rows8907 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8907 = true := by
  decide +kernel

theorem tot8907 : totK PD2M8K2 D2M8K2.t8907 = [154718732163, 454647090536, 259088104580, 16724868547, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
