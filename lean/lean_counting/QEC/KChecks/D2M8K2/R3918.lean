import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15672 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15672 = true := by
  decide +kernel

theorem tot15672 : totK PD2M8K2 D2M8K2.t15672 = [0, 0, 34608413148, 325078643572, 446994048536, 90916514924, 1242138600, 0] := by
  decide +kernel

theorem rows15673 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15673 = true := by
  decide +kernel

theorem tot15673 : totK PD2M8K2 D2M8K2.t15673 = [0, 0, 0, 215717207299, 470166714209, 169126986373, 7182288656, 0] := by
  decide +kernel

theorem rows15674 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15674 = true := by
  decide +kernel

theorem tot15674 : totK PD2M8K2 D2M8K2.t15674 = [0, 0, 143723674424, 354456803287, 267010554747, 122163023437, 13326740810, 0] := by
  decide +kernel

theorem rows15675 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15675 = true := by
  decide +kernel

theorem tot15675 : totK PD2M8K2 D2M8K2.t15675 = [0, 0, 182004481439, 448409048141, 223522644452, 13760705600, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
