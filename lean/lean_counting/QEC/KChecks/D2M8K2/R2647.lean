import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10588 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10588 = true := by
  decide +kernel

theorem tot10588 : totK PD2M8K2 D2M8K2.t10588 = [0, 0, 196397292235, 474954275395, 213279144338, 12183533023, 0, 0] := by
  decide +kernel

theorem rows10589 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10589 = true := by
  decide +kernel

theorem tot10589 : totK PD2M8K2 D2M8K2.t10589 = [0, 0, 189278310711, 485524604139, 203462994090, 10629518131, 0, 0] := by
  decide +kernel

theorem rows10590 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10590 = true := by
  decide +kernel

theorem tot10590 : totK PD2M8K2 D2M8K2.t10590 = [0, 0, 159320101029, 467955536183, 248645426518, 13792379419, 0, 0] := by
  decide +kernel

theorem rows10591 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10591 = true := by
  decide +kernel

theorem tot10591 : totK PD2M8K2 D2M8K2.t10591 = [0, 0, 91298305516, 353016646304, 345762893536, 59449605844, 1021600638, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
