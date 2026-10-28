import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7588 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7588 = true := by
  decide +kernel

theorem tot7588 : totK PD2M8K2 D2M8K2.t7588 = [0, 0, 174689140974, 441843858487, 258819602006, 25116492387, 0, 0] := by
  decide +kernel

theorem rows7589 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7589 = true := by
  decide +kernel

theorem tot7589 : totK PD2M8K2 D2M8K2.t7589 = [0, 0, 200877168512, 500209482266, 198950732831, 5430665091, 0, 0] := by
  decide +kernel

theorem rows7590 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7590 = true := by
  decide +kernel

theorem tot7590 : totK PD2M8K2 D2M8K2.t7590 = [0, 173043034316, 409226803714, 230753750648, 86377018282, 5354502914, 0, 0] := by
  decide +kernel

theorem rows7591 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7591 = true := by
  decide +kernel

theorem tot7591 : totK PD2M8K2 D2M8K2.t7591 = [0, 180827484454, 462123375141, 245721153957, 18008324577, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
