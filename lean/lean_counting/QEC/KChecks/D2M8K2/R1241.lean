import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4964 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4964 = true := by
  decide +kernel

theorem tot4964 : totK PD2M8K2 D2M8K2.t4964 = [0, 0, 204998437321, 473247091828, 213002146165, 12208674056, 0, 0] := by
  decide +kernel

theorem rows4965 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4965 = true := by
  decide +kernel

theorem tot4965 : totK PD2M8K2 D2M8K2.t4965 = [0, 57711587728, 224509680271, 417417481224, 195459232520, 8214505460, 0, 0] := by
  decide +kernel

theorem rows4966 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4966 = true := by
  decide +kernel

theorem tot4966 : totK PD2M8K2 D2M8K2.t4966 = [0, 185735825883, 468782307776, 250007606369, 23389423654, 0, 0, 0] := by
  decide +kernel

theorem rows4967 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4967 = true := by
  decide +kernel

theorem tot4967 : totK PD2M8K2 D2M8K2.t4967 = [0, 166663425211, 475113280541, 248776845742, 12346377983, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
