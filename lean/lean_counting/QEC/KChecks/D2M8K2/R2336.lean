import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9344 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9344 = true := by
  decide +kernel

theorem tot9344 : totK PD2M8K2 D2M8K2.t9344 = [0, 0, 0, 312350923404, 433096499804, 79249210859, 1209030869, 0] := by
  decide +kernel

theorem rows9345 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9345 = true := by
  decide +kernel

theorem tot9345 : totK PD2M8K2 D2M8K2.t9345 = [0, 0, 226761684884, 494055452630, 155974783967, 2519764721, 0, 0] := by
  decide +kernel

theorem rows9346 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9346 = true := by
  decide +kernel

theorem tot9346 : totK PD2M8K2 D2M8K2.t9346 = [0, 0, 225790469395, 462483518375, 170135523733, 11026950091, 0, 0] := by
  decide +kernel

theorem rows9347 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9347 = true := by
  decide +kernel

theorem tot9347 : totK PD2M8K2 D2M8K2.t9347 = [0, 0, 201421867568, 487963529064, 189116400706, 9836604324, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
