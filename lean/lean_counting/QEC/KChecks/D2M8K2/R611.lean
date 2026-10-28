import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2444 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2444 = true := by
  decide +kernel

theorem tot2444 : totK PD2M8K2 D2M8K2.t2444 = [0, 233620943544, 486951982246, 173243820814, 9450437173, 0, 0, 0] := by
  decide +kernel

theorem rows2445 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2445 = true := by
  decide +kernel

theorem tot2445 : totK PD2M8K2 D2M8K2.t2445 = [102247145681, 337639403080, 353368700469, 91947415183, 3434488093, 0, 0, 0] := by
  decide +kernel

theorem rows2446 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2446 = true := by
  decide +kernel

theorem tot2446 : totK PD2M8K2 D2M8K2.t2446 = [162855792140, 444025211908, 281845663222, 30620959717, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2447 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2447 = true := by
  decide +kernel

theorem tot2447 : totK PD2M8K2 D2M8K2.t2447 = [153654261150, 454131625795, 277534996159, 19570758928, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
