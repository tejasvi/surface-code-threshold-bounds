import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4584 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4584 = true := by
  decide +kernel

theorem tot4584 : totK PD2M8K2 D2M8K2.t4584 = [0, 0, 204166223911, 472047066706, 206405459149, 12146368384, 0, 0] := by
  decide +kernel

theorem rows4585 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4585 = true := by
  decide +kernel

theorem tot4585 : totK PD2M8K2 D2M8K2.t4585 = [0, 0, 19168557488, 326421685740, 452595171202, 74954456368, 1062926506, 0] := by
  decide +kernel

theorem rows4586 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4586 = true := by
  decide +kernel

theorem tot4586 : totK PD2M8K2 D2M8K2.t4586 = [0, 0, 63278519855, 288603497119, 421852634212, 103712279337, 3783381897, 0] := by
  decide +kernel

theorem rows4587 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4587 = true := by
  decide +kernel

theorem tot4587 : totK PD2M8K2 D2M8K2.t4587 = [0, 0, 185364390189, 464401102305, 246466345386, 22719114835, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
