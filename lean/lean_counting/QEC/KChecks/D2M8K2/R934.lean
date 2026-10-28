import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3736 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3736 = true := by
  decide +kernel

theorem tot3736 : totK PD2M8K2 D2M8K2.t3736 = [19691318959, 314708116366, 467948591636, 103917594072, 1267860612, 0, 0, 0] := by
  decide +kernel

theorem rows3737 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3737 = true := by
  decide +kernel

theorem tot3737 : totK PD2M8K2 D2M8K2.t3737 = [0, 211665485280, 478128090664, 185320756930, 7430810494, 0, 0, 0] := by
  decide +kernel

theorem rows3738 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3738 = true := by
  decide +kernel

theorem tot3738 : totK PD2M8K2 D2M8K2.t3738 = [0, 157347312568, 434192598665, 292644584782, 35405910377, 0, 0, 0] := by
  decide +kernel

theorem rows3739 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3739 = true := by
  decide +kernel

theorem tot3739 : totK PD2M8K2 D2M8K2.t3739 = [0, 188036196698, 471433959499, 242589691711, 12892902244, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
