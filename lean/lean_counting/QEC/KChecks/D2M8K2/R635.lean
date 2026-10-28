import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2540 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2540 = true := by
  decide +kernel

theorem tot2540 : totK PD2M8K2 D2M8K2.t2540 = [0, 193795193396, 475721048333, 224439569318, 12439805748, 0, 0, 0] := by
  decide +kernel

theorem rows2541 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2541 = true := by
  decide +kernel

theorem tot2541 : totK PD2M8K2 D2M8K2.t2541 = [0, 52277709162, 329090528840, 410050644317, 83300031971, 1171084559, 0, 0] := by
  decide +kernel

theorem rows2542 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2542 = true := by
  decide +kernel

theorem tot2542 : totK PD2M8K2 D2M8K2.t2542 = [0, 0, 199122482103, 456155071453, 185278438578, 11934365838, 0, 0] := by
  decide +kernel

theorem rows2543 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2543 = true := by
  decide +kernel

theorem tot2543 : totK PD2M8K2 D2M8K2.t2543 = [0, 163281325637, 454762636131, 263080897831, 20916963355, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
