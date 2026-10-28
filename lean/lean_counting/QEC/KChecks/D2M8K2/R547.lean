import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2188 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2188 = true := by
  decide +kernel

theorem tot2188 : totK PD2M8K2 D2M8K2.t2188 = [0, 0, 135928871182, 419825402927, 317725654088, 29243809989, 0, 0] := by
  decide +kernel

theorem rows2189 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2189 = true := by
  decide +kernel

theorem tot2189 : totK PD2M8K2 D2M8K2.t2189 = [0, 0, 182482360832, 497778553703, 207389748731, 8500385581, 0, 0] := by
  decide +kernel

theorem rows2190 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2190 = true := by
  decide +kernel

theorem tot2190 : totK PD2M8K2 D2M8K2.t2190 = [0, 0, 203597648210, 481694482820, 203578338487, 7831578770, 0, 0] := by
  decide +kernel

theorem rows2191 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2191 = true := by
  decide +kernel

theorem tot2191 : totK PD2M8K2 D2M8K2.t2191 = [0, 0, 182717430043, 463438298102, 243822957500, 18325117205, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
