import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9640 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9640 = true := by
  decide +kernel

theorem tot9640 : totK PD2M8K2 D2M8K2.t9640 = [0, 0, 187527911038, 479274700114, 205450206790, 10133036384, 0, 0] := by
  decide +kernel

theorem rows9641 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9641 = true := by
  decide +kernel

theorem tot9641 : totK PD2M8K2 D2M8K2.t9641 = [0, 0, 219220066759, 500740074555, 149021333453, 2330587781, 0, 0] := by
  decide +kernel

theorem rows9642 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9642 = true := by
  decide +kernel

theorem tot9642 : totK PD2M8K2 D2M8K2.t9642 = [0, 0, 160516007205, 487279150703, 224503058351, 6169546865, 0, 0] := by
  decide +kernel

theorem rows9643 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9643 = true := by
  decide +kernel

theorem tot9643 : totK PD2M8K2 D2M8K2.t9643 = [0, 0, 201251872386, 465938089201, 196392919446, 11003955353, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
