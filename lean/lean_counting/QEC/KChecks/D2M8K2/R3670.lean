import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14680 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14680 = true := by
  decide +kernel

theorem tot14680 : totK PD2M8K2 D2M8K2.t14680 = [0, 0, 37670822061, 348522051132, 379776331056, 60172979559, 1032241984, 0] := by
  decide +kernel

theorem rows14681 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14681 = true := by
  decide +kernel

theorem tot14681 : totK PD2M8K2 D2M8K2.t14681 = [0, 0, 83708212036, 303778452496, 358882494727, 91795793793, 3598673838, 0] := by
  decide +kernel

theorem rows14682 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14682 = true := by
  decide +kernel

theorem tot14682 : totK PD2M8K2 D2M8K2.t14682 = [0, 0, 211817387778, 473906072813, 201749598803, 11367430297, 0, 0] := by
  decide +kernel

theorem rows14683 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14683 = true := by
  decide +kernel

theorem tot14683 : totK PD2M8K2 D2M8K2.t14683 = [0, 71990150170, 228332908599, 384306369363, 208892188510, 15086715677, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
