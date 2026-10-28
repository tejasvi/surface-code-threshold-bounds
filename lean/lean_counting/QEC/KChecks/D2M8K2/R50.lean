import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows200 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t200 = true := by
  decide +kernel

theorem tot200 : totK PD2M8K2 D2M8K2.t200 = [0, 0, 190557918365, 476381837392, 197589400120, 12434957066, 0, 0] := by
  decide +kernel

theorem rows201 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t201 = true := by
  decide +kernel

theorem tot201 : totK PD2M8K2 D2M8K2.t201 = [0, 0, 211478527464, 478202691695, 177830284441, 9782461661, 0, 0] := by
  decide +kernel

theorem rows202 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t202 = true := by
  decide +kernel

theorem tot202 : totK PD2M8K2 D2M8K2.t202 = [0, 0, 197392712095, 478407434923, 186030571217, 12436117259, 0, 0] := by
  decide +kernel

theorem rows203 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t203 = true := by
  decide +kernel

theorem tot203 : totK PD2M8K2 D2M8K2.t203 = [0, 0, 202162090211, 479011305875, 176120411883, 9609506048, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
