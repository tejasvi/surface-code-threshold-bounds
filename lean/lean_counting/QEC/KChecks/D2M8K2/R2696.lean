import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10784 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10784 = true := by
  decide +kernel

theorem tot10784 : totK PD2M8K2 D2M8K2.t10784 = [0, 171794632953, 440548953497, 256537282538, 20934085980, 0, 0, 0] := by
  decide +kernel

theorem rows10785 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10785 = true := by
  decide +kernel

theorem tot10785 : totK PD2M8K2 D2M8K2.t10785 = [0, 92937627352, 348747400217, 381743678390, 84143167959, 1268739303, 0, 0] := by
  decide +kernel

theorem rows10786 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10786 = true := by
  decide +kernel

theorem tot10786 : totK PD2M8K2 D2M8K2.t10786 = [0, 0, 235337964602, 479265060801, 157277799077, 4764360615, 0, 0] := by
  decide +kernel

theorem rows10787 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10787 = true := by
  decide +kernel

theorem tot10787 : totK PD2M8K2 D2M8K2.t10787 = [0, 0, 184110442286, 468135015985, 227324675697, 17385499678, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
