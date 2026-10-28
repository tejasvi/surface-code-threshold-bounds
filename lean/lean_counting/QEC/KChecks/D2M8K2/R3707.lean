import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14828 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14828 = true := by
  decide +kernel

theorem tot14828 : totK PD2M8K2 D2M8K2.t14828 = [0, 182241145137, 459324924257, 245874813640, 22683934907, 0, 0, 0] := by
  decide +kernel

theorem rows14829 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14829 = true := by
  decide +kernel

theorem tot14829 : totK PD2M8K2 D2M8K2.t14829 = [0, 196409815832, 473975091387, 212065894330, 12183533023, 0, 0, 0] := by
  decide +kernel

theorem rows14830 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14830 = true := by
  decide +kernel

theorem tot14830 : totK PD2M8K2 D2M8K2.t14830 = [0, 56627033482, 346345239831, 398851137786, 79600225285, 1162935789, 0, 0] := by
  decide +kernel

theorem rows14831 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14831 = true := by
  decide +kernel

theorem tot14831 : totK PD2M8K2 D2M8K2.t14831 = [0, 0, 200238603860, 447382492221, 184749626361, 11853261585, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
