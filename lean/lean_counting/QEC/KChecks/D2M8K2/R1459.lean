import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5836 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5836 = true := by
  decide +kernel

theorem tot5836 : totK PD2M8K2 D2M8K2.t5836 = [186227045703, 454702706324, 251550187378, 19587653496, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5837 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5837 = true := by
  decide +kernel

theorem tot5837 : totK PD2M8K2 D2M8K2.t5837 = [63020407318, 332041169732, 407813752107, 94094787418, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows5838 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5838 = true := by
  decide +kernel

theorem tot5838 : totK PD2M8K2 D2M8K2.t5838 = [0, 206738552914, 489210839331, 179972165568, 7287134398, 0, 0, 0] := by
  decide +kernel

theorem rows5839 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5839 = true := by
  decide +kernel

theorem tot5839 : totK PD2M8K2 D2M8K2.t5839 = [0, 190308341833, 472810742654, 218294632167, 14692331624, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
