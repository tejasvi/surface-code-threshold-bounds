import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6860 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6860 = true := by
  decide +kernel

theorem tot6860 : totK PD2M8K2 D2M8K2.t6860 = [0, 160609534383, 445807148362, 279107522203, 21338422429, 0, 0, 0] := by
  decide +kernel

theorem rows6861 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6861 = true := by
  decide +kernel

theorem tot6861 : totK PD2M8K2 D2M8K2.t6861 = [90585905067, 287245792451, 335816176954, 178344827919, 17381733283, 0, 0, 0] := by
  decide +kernel

theorem rows6862 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6862 = true := by
  decide +kernel

theorem tot6862 : totK PD2M8K2 D2M8K2.t6862 = [169749124370, 452713869843, 238969538288, 16894351549, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6863 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6863 = true := by
  decide +kernel

theorem tot6863 : totK PD2M8K2 D2M8K2.t6863 = [153689042697, 444138998400, 276309236311, 22261400269, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
