import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2680 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2680 = true := by
  decide +kernel

theorem tot2680 : totK PA10K2 A10K2.t2680 = [0, 0, 565049170806, 1964326309016, 1902325121608, 444670935536, 13227942247, 0, 0, 0] := by
  decide +kernel

theorem rows2681 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2681 = true := by
  decide +kernel

theorem tot2681 : totK PA10K2 A10K2.t2681 = [0, 0, 446598500918, 1678436243195, 1881084557044, 562237520876, 50267370225, 0, 0, 0] := by
  decide +kernel

theorem rows2682 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2682 = true := by
  decide +kernel

theorem tot2682 : totK PA10K2 A10K2.t2682 = [0, 0, 250617950027, 1463933509468, 2103843942192, 724576637037, 52130376097, 0, 0, 0] := by
  decide +kernel

theorem rows2683 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2683 = true := by
  decide +kernel

theorem tot2683 : totK PA10K2 A10K2.t2683 = [0, 311517321411, 947359473088, 1066246376781, 1262254989058, 945718553708, 213642913445, 6354482628, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
