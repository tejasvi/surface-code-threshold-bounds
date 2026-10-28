import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2900 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2900 = true := by
  decide +kernel

theorem tot2900 : totK PD2M8K2 D2M8K2.t2900 = [22688559126, 321039350752, 489727619401, 72175898220, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2901 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2901 = true := by
  decide +kernel

theorem tot2901 : totK PD2M8K2 D2M8K2.t2901 = [163638602761, 438487715565, 277215052848, 30465585733, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2902 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2902 = true := by
  decide +kernel

theorem tot2902 : totK PD2M8K2 D2M8K2.t2902 = [199686042129, 484364814573, 224525234227, 12237037258, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2903 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2903 = true := by
  decide +kernel

theorem tot2903 : totK PD2M8K2 D2M8K2.t2903 = [25531115907, 265600641121, 414624417713, 191123752303, 21385708972, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
