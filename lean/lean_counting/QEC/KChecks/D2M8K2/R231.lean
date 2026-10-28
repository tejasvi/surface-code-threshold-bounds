import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows924 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t924 = true := by
  decide +kernel

theorem tot924 : totK PD2M8K2 D2M8K2.t924 = [45526847365, 207614450271, 413389250417, 232302406670, 17433533548, 0, 0, 0] := by
  decide +kernel

theorem rows925 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t925 = true := by
  decide +kernel

theorem tot925 : totK PD2M8K2 D2M8K2.t925 = [163895174698, 442090155757, 278200399552, 30365573906, 0, 0, 0, 0] := by
  decide +kernel

theorem rows926 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t926 = true := by
  decide +kernel

theorem tot926 : totK PD2M8K2 D2M8K2.t926 = [197603347015, 476653165245, 224038507012, 12148017968, 0, 0, 0, 0] := by
  decide +kernel

theorem rows927 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t927 = true := by
  decide +kernel

theorem tot927 : totK PD2M8K2 D2M8K2.t927 = [19080408929, 263188296108, 421357231108, 192735542345, 21400436502, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
