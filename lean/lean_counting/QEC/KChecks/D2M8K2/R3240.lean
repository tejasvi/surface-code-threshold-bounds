import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12960 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12960 = true := by
  decide +kernel

theorem tot12960 : totK PD2M8K2 D2M8K2.t12960 = [0, 0, 172144234727, 488543462980, 217353146258, 6595102474, 0, 0] := by
  decide +kernel

theorem rows12961 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12961 = true := by
  decide +kernel

theorem tot12961 : totK PD2M8K2 D2M8K2.t12961 = [0, 176559373540, 434549142124, 241689033928, 60755518003, 4185467556, 0, 0] := by
  decide +kernel

theorem rows12962 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12962 = true := by
  decide +kernel

theorem tot12962 : totK PD2M8K2 D2M8K2.t12962 = [0, 181097966188, 479547882819, 236647922237, 15394402876, 0, 0, 0] := by
  decide +kernel

theorem rows12963 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12963 = true := by
  decide +kernel

theorem tot12963 : totK PD2M8K2 D2M8K2.t12963 = [0, 88269248588, 332556405613, 390329579203, 85232859499, 1164319620, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
