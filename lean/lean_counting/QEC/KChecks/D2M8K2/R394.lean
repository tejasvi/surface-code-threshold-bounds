import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1576 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1576 = true := by
  decide +kernel

theorem tot1576 : totK PD2M8K2 D2M8K2.t1576 = [0, 165324708119, 469748037033, 244443934246, 13672237646, 0, 0, 0] := by
  decide +kernel

theorem rows1577 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1577 = true := by
  decide +kernel

theorem tot1577 : totK PD2M8K2 D2M8K2.t1577 = [0, 0, 219300143123, 475478860845, 199702054591, 8070752097, 0, 0] := by
  decide +kernel

theorem rows1578 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1578 = true := by
  decide +kernel

theorem tot1578 : totK PD2M8K2 D2M8K2.t1578 = [0, 50849869571, 236701386591, 422031556295, 173080923855, 5648725239, 0, 0] := by
  decide +kernel

theorem rows1579 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1579 = true := by
  decide +kernel

theorem tot1579 : totK PD2M8K2 D2M8K2.t1579 = [0, 191226484792, 462764615794, 242428528872, 20664791887, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
