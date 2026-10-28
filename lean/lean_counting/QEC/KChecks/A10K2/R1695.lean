import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6780 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6780 = true := by
  decide +kernel

theorem tot6780 : totK PA10K2 A10K2.t6780 = [0, 253046812372, 1092548694934, 1891600988836, 1365719378018, 281695784146, 10956717587, 0, 0, 0] := by
  decide +kernel

theorem rows6781 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6781 = true := by
  decide +kernel

theorem tot6781 : totK PA10K2 A10K2.t6781 = [0, 492752704009, 1812620956011, 2031778861887, 620582814779, 37431387394, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6782 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6782 = true := by
  decide +kernel

theorem tot6782 : totK PA10K2 A10K2.t6782 = [0, 122360162702, 995766830729, 2160553956856, 1480491721451, 232847548213, 6281495166, 0, 0, 0] := by
  decide +kernel

theorem rows6783 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6783 = true := by
  decide +kernel

theorem tot6783 : totK PA10K2 A10K2.t6783 = [0, 0, 612056063578, 2055426274571, 1906345624676, 453102095803, 12813073358, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
