import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15064 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15064 = true := by
  decide +kernel

theorem tot15064 : totK PD2M8K2 D2M8K2.t15064 = [0, 0, 93587166913, 347885107902, 374954000106, 82460960618, 1242138600, 0] := by
  decide +kernel

theorem rows15065 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15065 = true := by
  decide +kernel

theorem tot15065 : totK PD2M8K2 D2M8K2.t15065 = [0, 0, 0, 237499946029, 472723719247, 145338020640, 4600645648, 0] := by
  decide +kernel

theorem rows15066 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15066 = true := by
  decide +kernel

theorem tot15066 : totK PD2M8K2 D2M8K2.t15066 = [0, 92342479873, 211464003830, 164836433779, 257693695028, 151488759652, 14896018734, 0] := by
  decide +kernel

theorem rows15067 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15067 = true := by
  decide +kernel

theorem tot15067 : totK PD2M8K2 D2M8K2.t15067 = [0, 175504638366, 467139804314, 245077749037, 17115888737, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
