import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1604 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1604 = true := by
  decide +kernel

theorem tot1604 : totK PD2M8K2 D2M8K2.t1604 = [0, 0, 164460505918, 392065667964, 245159818445, 64905775023, 3667207281, 0] := by
  decide +kernel

theorem rows1605 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1605 = true := by
  decide +kernel

theorem tot1605 : totK PD2M8K2 D2M8K2.t1605 = [0, 0, 156595344638, 455816951047, 263690045074, 16944958282, 0, 0] := by
  decide +kernel

theorem rows1606 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1606 = true := by
  decide +kernel

theorem tot1606 : totK PD2M8K2 D2M8K2.t1606 = [0, 101307309327, 325877852614, 320543210841, 145088475435, 13566916688, 0, 0] := by
  decide +kernel

theorem rows1607 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1607 = true := by
  decide +kernel

theorem tot1607 : totK PD2M8K2 D2M8K2.t1607 = [0, 179113476057, 460230390099, 235475705902, 17115888737, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
