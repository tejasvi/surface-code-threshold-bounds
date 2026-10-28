import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4040 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4040 = true := by
  decide +kernel

theorem tot4040 : totK PD2M8K2 D2M8K2.t4040 = [0, 0, 0, 209785244462, 480569257469, 192013529659, 7658844075, 0] := by
  decide +kernel

theorem rows4041 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4041 = true := by
  decide +kernel

theorem tot4041 : totK PD2M8K2 D2M8K2.t4041 = [0, 0, 66225297140, 250434935609, 386702971898, 168817139756, 7877424857, 0] := by
  decide +kernel

theorem rows4042 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4042 = true := by
  decide +kernel

theorem tot4042 : totK PD2M8K2 D2M8K2.t4042 = [0, 0, 182226624387, 453259725891, 266647317246, 27645928171, 0, 0] := by
  decide +kernel

theorem rows4043 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4043 = true := by
  decide +kernel

theorem tot4043 : totK PD2M8K2 D2M8K2.t4043 = [0, 0, 172383748415, 467364341752, 242424989194, 10742735399, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
