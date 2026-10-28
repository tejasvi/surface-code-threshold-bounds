import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4100 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4100 = true := by
  decide +kernel

theorem tot4100 : totK PD2M8K2 D2M8K2.t4100 = [0, 163411705972, 450609890769, 287916953836, 30437197709, 0, 0, 0] := by
  decide +kernel

theorem rows4101 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4101 = true := by
  decide +kernel

theorem tot4101 : totK PD2M8K2 D2M8K2.t4101 = [0, 175404056910, 466990576626, 247260404500, 17212296787, 0, 0, 0] := by
  decide +kernel

theorem rows4102 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4102 = true := by
  decide +kernel

theorem tot4102 : totK PD2M8K2 D2M8K2.t4102 = [0, 0, 244997438769, 512935760357, 141041294063, 2348440009, 0, 0] := by
  decide +kernel

theorem rows4103 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4103 = true := by
  decide +kernel

theorem tot4103 : totK PD2M8K2 D2M8K2.t4103 = [0, 50692750027, 248385115685, 411230429251, 158411730962, 10902245252, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
