import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1740 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1740 = true := by
  decide +kernel

theorem tot1740 : totK PD2M8K2 D2M8K2.t1740 = [0, 0, 91570842872, 390630319553, 368363756965, 50769950177, 1232609433, 0] := by
  decide +kernel

theorem rows1741 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1741 = true := by
  decide +kernel

theorem tot1741 : totK PD2M8K2 D2M8K2.t1741 = [0, 0, 0, 268766412755, 480426038368, 127830186112, 3724448267, 0] := by
  decide +kernel

theorem rows1742 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1742 = true := by
  decide +kernel

theorem tot1742 : totK PD2M8K2 D2M8K2.t1742 = [0, 0, 155398357114, 369189989866, 263511501420, 93816197092, 8757608180, 0] := by
  decide +kernel

theorem rows1743 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1743 = true := by
  decide +kernel

theorem tot1743 : totK PD2M8K2 D2M8K2.t1743 = [0, 0, 173085026625, 450022927846, 233949069086, 17115888737, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
