import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1512 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1512 = true := by
  decide +kernel

theorem tot1512 : totK PD2M8K2 D2M8K2.t1512 = [0, 188213933825, 446568155171, 248037542375, 23877706993, 0, 0, 0] := by
  decide +kernel

theorem rows1513 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1513 = true := by
  decide +kernel

theorem tot1513 : totK PD2M8K2 D2M8K2.t1513 = [0, 138442984036, 450045081731, 289664918359, 20074333972, 0, 0, 0] := by
  decide +kernel

theorem rows1514 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1514 = true := by
  decide +kernel

theorem tot1514 : totK PD2M8K2 D2M8K2.t1514 = [0, 0, 198188185075, 483554595966, 186063527740, 9668735432, 0, 0] := by
  decide +kernel

theorem rows1515 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1515 = true := by
  decide +kernel

theorem tot1515 : totK PD2M8K2 D2M8K2.t1515 = [0, 87770539582, 313709794602, 377489995023, 105473289239, 3581949829, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
