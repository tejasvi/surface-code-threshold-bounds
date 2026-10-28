import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8788 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8788 = true := by
  decide +kernel

theorem tot8788 : totK PD2M8K2 D2M8K2.t8788 = [0, 0, 261624387604, 503205138826, 129086014769, 3884009855, 0, 0] := by
  decide +kernel

theorem rows8789 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8789 = true := by
  decide +kernel

theorem tot8789 : totK PD2M8K2 D2M8K2.t8789 = [0, 0, 183093323046, 490606024791, 179981496399, 3708492342, 0, 0] := by
  decide +kernel

theorem rows8790 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8790 = true := by
  decide +kernel

theorem tot8790 : totK PD2M8K2 D2M8K2.t8790 = [0, 0, 180223717949, 471555201287, 234281270932, 18701993290, 0, 0] := by
  decide +kernel

theorem rows8791 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8791 = true := by
  decide +kernel

theorem tot8791 : totK PD2M8K2 D2M8K2.t8791 = [0, 0, 191148476458, 456624880644, 216663542143, 17398708553, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
