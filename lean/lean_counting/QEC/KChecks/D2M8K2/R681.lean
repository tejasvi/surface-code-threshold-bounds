import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2724 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2724 = true := by
  decide +kernel

theorem tot2724 : totK PD2M8K2 D2M8K2.t2724 = [0, 0, 54664046510, 423256194005, 368456185486, 27491478142, 0, 0] := by
  decide +kernel

theorem rows2725 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2725 = true := by
  decide +kernel

theorem tot2725 : totK PD2M8K2 D2M8K2.t2725 = [0, 0, 101780523232, 334217972029, 359456385699, 69356604455, 1271866555, 0] := by
  decide +kernel

theorem rows2726 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2726 = true := by
  decide +kernel

theorem tot2726 : totK PD2M8K2 D2M8K2.t2726 = [0, 0, 199530912734, 456322639856, 234814815215, 20763552483, 0, 0] := by
  decide +kernel

theorem rows2727 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2727 = true := by
  decide +kernel

theorem tot2727 : totK PD2M8K2 D2M8K2.t2727 = [0, 70882335681, 208033522121, 359190100806, 238807720039, 18566504420, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
