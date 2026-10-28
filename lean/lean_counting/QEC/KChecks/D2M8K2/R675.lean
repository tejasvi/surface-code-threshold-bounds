import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2700 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2700 = true := by
  decide +kernel

theorem tot2700 : totK PD2M8K2 D2M8K2.t2700 = [0, 0, 185760183189, 446519773879, 255673660852, 25298831311, 0, 0] := by
  decide +kernel

theorem rows2701 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2701 = true := by
  decide +kernel

theorem tot2701 : totK PD2M8K2 D2M8K2.t2701 = [0, 0, 203416165061, 496573581945, 192743007943, 5430665091, 0, 0] := by
  decide +kernel

theorem rows2702 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2702 = true := by
  decide +kernel

theorem tot2702 : totK PD2M8K2 D2M8K2.t2702 = [0, 171607033725, 387994922542, 237657087324, 98853019939, 6756203132, 0, 0] := by
  decide +kernel

theorem rows2703 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2703 = true := by
  decide +kernel

theorem tot2703 : totK PD2M8K2 D2M8K2.t2703 = [0, 180284548937, 456961298933, 259233689301, 18405470726, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
