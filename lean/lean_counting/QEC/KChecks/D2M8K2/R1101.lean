import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4404 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4404 = true := by
  decide +kernel

theorem tot4404 : totK PD2M8K2 D2M8K2.t4404 = [0, 154806073524, 382462115646, 282558109605, 78293645916, 2338431331, 0, 0] := by
  decide +kernel

theorem rows4405 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4405 = true := by
  decide +kernel

theorem tot4405 : totK PD2M8K2 D2M8K2.t4405 = [0, 166070992095, 442441906641, 280330277362, 30500119012, 0, 0, 0] := by
  decide +kernel

theorem rows4406 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4406 = true := by
  decide +kernel

theorem tot4406 : totK PD2M8K2 D2M8K2.t4406 = [0, 90950819051, 376705323577, 349793618980, 57467994552, 1096156699, 0, 0] := by
  decide +kernel

theorem rows4407 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4407 = true := by
  decide +kernel

theorem tot4407 : totK PD2M8K2 D2M8K2.t4407 = [0, 0, 336207213233, 519903690996, 74989009978, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
